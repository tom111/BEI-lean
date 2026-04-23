/-
Krull dimension preservation under integral ring extensions.

For `R → A` an integral ring extension with `R → A` injective, the Krull
dimensions agree: `ringKrullDim A = ringKrullDim R`.

Proof outline:
- `ringKrullDim A ≤ ringKrullDim R` via strict monotonicity of
  `PrimeSpectrum.comap (algebraMap R A)` (incomparability for integral
  extensions, `Ideal.comap_lt_comap_of_integral_mem_sdiff`);
- `ringKrullDim R ≤ ringKrullDim A` by starting with going-up
  (`Ideal.exists_ideal_over_prime_of_isIntegral`) to find a prime of `A`
  over the top of a chain in `R`, then chain-lifting via `HasGoingDown`
  (`Ideal.exists_ltSeries_of_hasGoingDown`).

The combined result is `ringKrullDim_eq_of_isIntegral_of_injective`.
-/

import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic

open Order Ideal

namespace Algebra.IsIntegral

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- For `A` integral over `R`, `PrimeSpectrum.comap (algebraMap R A)` is strictly
monotone. This is incomparability: distinct comparable primes of `A` have
distinct comaps in `R`. -/
lemma strictMono_primeSpectrum_comap [Algebra.IsIntegral R A] :
    StrictMono (PrimeSpectrum.comap (algebraMap R A)) := by
  intro P Q hPQ
  have hPQ' : P.asIdeal < Q.asIdeal := hPQ
  obtain ⟨hle, x, hxQ, hxP⟩ := SetLike.lt_iff_le_and_exists.mp hPQ'
  have hx_int : IsIntegral R x := Algebra.IsIntegral.isIntegral x
  have hlt : P.asIdeal.comap (algebraMap R A) < Q.asIdeal.comap (algebraMap R A) :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ hx_int
  exact hlt

/-- For integral extensions, `ringKrullDim A ≤ ringKrullDim R`. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R :=
  krullDim_le_of_strictMono _ strictMono_primeSpectrum_comap

end Algebra.IsIntegral

section GoingUpChain

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Going-up chain lift for integral extensions. Given an `LTSeries` in
`PrimeSpectrum R`, find an `LTSeries` of the same length in `PrimeSpectrum A`
whose entries lie over those of the original series, starting from any
prime `I₀` of `A` with `I₀.comap ≤ l.head`.

This is the classical Cohen–Seidenberg going-up theorem, phrased as a chain
lift. Mathlib has the analogous statement for going-down
(`Ideal.exists_ltSeries_of_hasGoingDown`); the going-up version is proved here
from the prime-lifting lemma `Ideal.exists_ideal_over_prime_of_isIntegral`. -/
theorem exists_ltSeries_of_isIntegral_of_comap_le [Algebra.IsIntegral R A]
    (l : LTSeries (PrimeSpectrum R)) (I₀ : Ideal A)
    (hI₀ : I₀.comap (algebraMap R A) ≤ l.head.asIdeal) :
    ∃ (L : LTSeries (PrimeSpectrum A)),
      L.length = l.length ∧
      L.last.asIdeal.comap (algebraMap R A) = l.last.asIdeal := by
  induction l using RelSeries.inductionOn' with
  | singleton q =>
    -- Base case: l is the singleton [q]
    haveI : q.asIdeal.IsPrime := q.2
    have hcomap_le : I₀.comap (algebraMap R A) ≤ q.asIdeal := by simpa using hI₀
    obtain ⟨Q, -, hQ_prime, hQ_over⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral
        (R := R) (S := A) q.asIdeal I₀ hcomap_le
    exact ⟨RelSeries.singleton _ ⟨Q, hQ_prime⟩, rfl, by simpa using hQ_over⟩
  | snoc p q hq ih =>
    -- Snoc case: (p.snoc q hq) extends p at the end by q with p.last < q
    -- First lift p by IH (head unchanged under snoc)
    have hhead : p.head = (p.snoc q hq).head := by simp
    have hI₀_le : I₀.comap (algebraMap R A) ≤ p.head.asIdeal := by
      rw [hhead]; simpa using hI₀
    obtain ⟨L', hLlen, hLlast⟩ := ih hI₀_le
    haveI : L'.last.asIdeal.IsPrime := L'.last.2
    haveI : q.asIdeal.IsPrime := q.2
    -- p.last < q as PrimeSpectrum R (hq is `(p.last, q) ∈ {(a,b) | a < b}`)
    have hlt : p.last < q := hq
    have hlt_ideal : p.last.asIdeal < q.asIdeal := hlt
    -- L'.last.asIdeal.comap = p.last.asIdeal, and p.last < q
    -- So extend L' by a prime Q ≥ L'.last over q.asIdeal (going-up)
    obtain ⟨Q, hLQ, hQ_prime, hQ_over⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral
        (R := R) (S := A) q.asIdeal L'.last.asIdeal
        (by rw [hLlast]; exact hlt_ideal.le)
    -- L'.last ≠ Q: their comaps differ since p.last < q
    have hne : L'.last.asIdeal ≠ Q := fun h => by
      rw [h, hQ_over] at hLlast
      exact (ne_of_lt hlt_ideal) hLlast.symm
    have hlt_sub :
        (⟨L'.last.asIdeal, L'.last.2⟩ : PrimeSpectrum A) < ⟨Q, hQ_prime⟩ :=
      lt_of_le_of_ne hLQ (fun h => hne (PrimeSpectrum.ext_iff.mp h))
    refine ⟨RelSeries.snoc L' ⟨Q, hQ_prime⟩ hlt_sub, ?_, ?_⟩
    · simp [hLlen]
    · simpa using hQ_over

/-- Dimension lower bound via going-up for integral extensions.
If `A` is integral over `R` and the kernel of `R → A` is `⊥` (equivalently
`R → A` is injective), then chains of primes in `R` lift to chains in `A`
of the same length, so `ringKrullDim R ≤ ringKrullDim A`. -/
theorem ringKrullDim_ge_of_isIntegral_of_ker_le_bot
    [Algebra.IsIntegral R A]
    (hker : RingHom.ker (algebraMap R A) ≤ (⊥ : Ideal R)) :
    ringKrullDim R ≤ ringKrullDim A := by
  unfold ringKrullDim
  refine iSup_le fun l => ?_
  obtain ⟨L, hLlen, -⟩ :=
    exists_ltSeries_of_isIntegral_of_comap_le (R := R) (A := A) l (⊥ : Ideal A)
      (by
        intro r hr
        have : r ∈ (⊥ : Ideal R) := hker (by simpa [RingHom.mem_ker] using hr)
        exact (Ideal.mem_bot.mp this) ▸ l.head.asIdeal.zero_mem)
  calc (l.length : WithBot ℕ∞)
      = L.length := by rw [hLlen]
    _ ≤ ⨆ (q : LTSeries (PrimeSpectrum A)), (q.length : WithBot ℕ∞) :=
        le_iSup (fun q => (q.length : WithBot ℕ∞)) L

end GoingUpChain

section Combined

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- For `R → A` integral and injective, the Krull dimensions agree. No
flatness or going-down hypothesis is needed: the `≤` direction uses
incomparability, the `≥` direction uses the going-up chain lift. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective
    [Algebra.IsIntegral R A]
    (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R := by
  have hker : RingHom.ker (algebraMap R A) ≤ (⊥ : Ideal R) := by
    rw [RingHom.injective_iff_ker_eq_bot] at hinj
    rw [hinj]
  exact le_antisymm
    Algebra.IsIntegral.ringKrullDim_le_of_isIntegral
    (ringKrullDim_ge_of_isIntegral_of_ker_le_bot hker)

/-- For `A` module-finite over `R` with injective `R → A`, the Krull
dimensions agree. -/
theorem ringKrullDim_eq_of_finite_of_injective
    [Module.Finite R A]
    (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R :=
  have : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  ringKrullDim_eq_of_isIntegral_of_injective hinj

end Combined

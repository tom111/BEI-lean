import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Regular elements via minimal-prime avoidance

In a reduced ring, an element `r` is a non-zero-divisor iff it lies outside
every minimal prime. Combined with prime avoidance, this gives:

- `isSMulRegular_of_not_mem_minimalPrimes`: a sufficient NZD condition;
- `exists_smulRegular_in_inter`: in a reduced Noetherian ring, any prime `p`
  of positive height contains an element which is also in a non-minimal
  prime `m` and is regular on `R`.

These lemmas were originally `private` inside `BEI/Equidim.lean`. Their
statements use only standard ring-theoretic vocabulary.
-/

variable {S : Type*} [CommRing S]

/-- In a reduced ring, an element that lies outside every minimal prime is
a non-zero-divisor: in a reduced ring `sInf (minimalPrimes R) = 0`, so if
`r ∉ q` for each minimal prime `q`, then `r * s = 0` forces
`s ∈ ⋂ q = 0`. -/
lemma isSMulRegular_of_not_mem_minimalPrimes [IsReduced S]
    {r : S} (hr : ∀ q ∈ minimalPrimes S, r ∉ q) : IsSMulRegular S r := by
  intro a b hab
  have heq : r * a = r * b := by exact_mod_cast hab
  have h0 : r * (a - b) = 0 := by rw [mul_sub]; exact sub_eq_zero.mpr heq
  have hmem : a - b ∈ sInf (minimalPrimes S) := by
    rw [Ideal.mem_sInf]; intro q hq
    exact (((minimalPrimes_eq_minimals (R := S) ▸ hq).1).mem_or_mem
      (h0 ▸ q.zero_mem : r * (a - b) ∈ q)).resolve_left (hr q hq)
  rw [show sInf (minimalPrimes S) = (⊥ : Ideal S) from by
    change sInf ((⊥ : Ideal S).minimalPrimes) = ⊥
    rw [Ideal.sInf_minimalPrimes]; exact nilradical_eq_zero S, Ideal.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

/-- **Regular element in `p ∩ m` for reduced rings**: In a reduced Noetherian
ring where every minimal prime is below a non-minimal prime `m`, any prime
`p` of positive height contains an `R`-regular element that also lies in `m`.

The proof uses a domain-based argument: for each minimal prime `q`, we show
`p ⊓ m ⊄ q`. Since `q` is prime and both `p` and `m` strictly contain `q`
(by height and minimality considerations), taking `a ∈ p \ q` and `b ∈ m \ q`
gives `ab ∈ (p ⊓ m) \ q` by primality. Prime avoidance then produces an
element outside all minimal primes (hence regular). -/
theorem exists_smulRegular_in_inter [IsNoetherianRing S] [IsReduced S]
    (m : Ideal S) [m.IsPrime]
    (hmin_le : ∀ q ∈ minimalPrimes S, q ≤ m)
    (hm_ne_min : m ∉ minimalPrimes S)
    (p : Ideal S) [p.IsPrime]
    (hp : (0 : WithBot ℕ∞) < Ideal.height p) :
    ∃ x ∈ p, x ∈ m ∧ IsSMulRegular S x := by
  have hp_not_min : p ∉ minimalPrimes S := by
    intro hmin; simp [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff.mpr hmin] at hp
  -- Step 1: p ⊓ m ⊄ q for each minimal prime q
  have hp_inf_not_le : ∀ q ∈ minimalPrimes S, ¬(p ⊓ m ≤ q) := by
    intro q hq hle
    have hq_prime : q.IsPrime := (minimalPrimes_eq_minimals (R := S) ▸ hq).1
    -- p contains some minimal prime q'; since q' ≤ m, q' ≤ p ⊓ m ≤ q, hence q' = q
    obtain ⟨q', hq'min, hq'p⟩ :=
      Ideal.exists_minimalPrimes_le (show (⊥ : Ideal S) ≤ p from bot_le)
    have hq'minR : q' ∈ minimalPrimes S := hq'min
    have hq'q : q' ≤ q := le_trans (le_inf hq'p (hmin_le q' hq'minR)) hle
    have hq'eq : q' = q := le_antisymm hq'q
      ((minimalPrimes_eq_minimals (R := S) ▸ hq).2
        (minimalPrimes_eq_minimals (R := S) ▸ hq'minR).1 hq'q)
    -- So q ≤ p and q < p, q < m
    have hq_lt_p : q < p := lt_of_le_of_ne (hq'eq ▸ hq'p) (fun h => hp_not_min (h.symm ▸ hq))
    have hq_lt_m : q < m := lt_of_le_of_ne (hmin_le q hq) (fun h => hm_ne_min (h.symm ▸ hq))
    -- Domain argument: a ∈ p\q, b ∈ m\q, ab ∈ (p ⊓ m) \ q
    obtain ⟨a, hap, haq⟩ := Set.exists_of_ssubset hq_lt_p
    obtain ⟨b, hbm, hbq⟩ := Set.exists_of_ssubset hq_lt_m
    exact (hq_prime.mem_or_mem (hle ⟨p.mul_mem_right b hap, m.mul_mem_left a hbm⟩)).elim haq hbq
  -- Step 2: prime avoidance → ∃ x ∈ p ⊓ m outside all minimal primes
  have hfin : (minimalPrimes S).Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing S ⊥
  have h_not_sub : ¬((p ⊓ m : Set S) ⊆ ⋃ q ∈ minimalPrimes S, (q : Set S)) := by
    rw [show (p ⊓ m : Set S) = ↑(p ⊓ m : Ideal S) from rfl,
      Ideal.subset_union_prime_finite hfin 0 0
        (fun q hq _ _ => (minimalPrimes_eq_minimals (R := S) ▸ hq).1)]
    exact fun ⟨q, hq, hle⟩ => hp_inf_not_le q hq hle
  obtain ⟨x, hx_mem, hx_not_mem⟩ := Set.not_subset.mp h_not_sub
  simp only [Set.mem_iUnion] at hx_not_mem; push_neg at hx_not_mem
  exact ⟨x, hx_mem.1, hx_mem.2, isSMulRegular_of_not_mem_minimalPrimes hx_not_mem⟩
